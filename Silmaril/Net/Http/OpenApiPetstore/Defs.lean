module

public import Silmaril.Net.Http.OpenApi.Defs

/-!
# An OpenAPI example: a pet store

A small document in the modelled OpenAPI 3.1.0 subset, after the specification's pet store
example, and a service for it built from one handler per operation:

```yaml
openapi: 3.1.0
info: { title: Pets }
paths:
  /pets:
    get:  { operationId: listPets,
            parameters: [{ name: limit, in: query, schema: { type: integer, minimum: 1, maximum: 100 } }],
            responses: { "200": { content: { application/json: {} } } } }
    post: { operationId: createPet,
            requestBody: { required: true, content: { application/json: {} } },
            responses: { "201": { headers: { Location: {} } }, "4XX": {} } }
  /pets/mine:
    get:  { operationId: myPets, responses: { "200": { content: { application/json: {} } } } }
  /pets/{petId}:
    get:  { operationId: showPetById,
            parameters: [{ name: petId, in: path, required: true, schema: { type: string } }],
            responses: { "200": { content: { application/json: {} } }, "404": {} } }
```

`/pets/mine` is concrete, so it is matched before `/pets/{petId}`.
-/

@[expose] public section

namespace Silmaril.Net.Http.OpenApi.Petstore

open Silmaril.Net.Http

def json : Bytes := ascii "application/json"

def listPets : Operation :=
  ⟨.get, "listPets", [⟨ascii "limit", .query, false, .integer (some 1) (some 100)⟩], none,
    [(.code 200, ⟨[json], []⟩)]⟩

def createPet : Operation :=
  ⟨.post, "createPet", [], some ⟨true, [json]⟩,
    [(.code 201, ⟨[], [ascii "location"]⟩), (.range 4, ⟨[], []⟩)]⟩

def myPets : Operation := ⟨.get, "myPets", [], none, [(.code 200, ⟨[json], []⟩)]⟩

def showPetById : Operation :=
  ⟨.get, "showPetById", [⟨ascii "petId", .path, true, .string 1 none none⟩], none,
    [(.code 200, ⟨[json], []⟩), (.code 404, ⟨[], []⟩)]⟩

def doc : Document :=
  ⟨"3.1.0", "Pets",
    [⟨[.lit (ascii "pets")], [listPets, createPet]⟩,
     ⟨[.lit (ascii "pets"), .lit (ascii "mine")], [myPets]⟩,
     ⟨[.lit (ascii "pets"), .param (ascii "petId")], [showPetById]⟩]⟩

/-- A JSON response. -/
def jsonResponse (code : Nat) (body : String) : Response :=
  ⟨code, [⟨ascii "Content-Type", json⟩], ascii body, []⟩

/-- The handlers: one pet, with identifier `1`. -/
def handlers (op : Operation) (vs : List Bytes) (r : Request) : Response :=
  if op.operationId = "listPets" then jsonResponse 200 "[{\"id\":1}]"
  else if op.operationId = "createPet" then
    if r.content = [] then Response.simple 400 []
    else ⟨201, [⟨ascii "Location", ascii "/pets/1"⟩], [], []⟩
  else if op.operationId = "myPets" then jsonResponse 200 "[{\"id\":1}]"
  else if vs = [ascii "1"] then jsonResponse 200 "{\"id\":1}"
  else Response.simple 404 []

def service : Service := Service.ofHandlers doc handlers

end Silmaril.Net.Http.OpenApi.Petstore
